module

public import Flapjack.Compiler.Backend.WordGcFunctions

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_IMP_isWord"
  (words_as_type_indexed_bitvec)]
theorem wordGcMove_imp_isWord {width : Nat} [NeZero width] (conf : Config) (c i pa old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (w : WordLocW width) (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (h : wordGcMove conf (.word c, i, pa, old, m, dm) = (w, i1, pa1, m1, c1)) :
    wordSemIsWordLoc w = true := by
  cases w with
  | word value => rfl
  | loc block offset =>
      simp only [wordGcMove] at h
      repeat' (split at h) <;> simp_all [wordSemIsWordLoc]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_IMP_isWord"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_imp_isWord {width : Nat} [NeZero width] (conf : Config) (c i pa ib pb old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (w : WordLocW width) (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (h : wordGenGcMove conf (.word c, i, pa, ib, pb, old, m, dm) = (w, i1, pa1, ib1, pb1, m1, c1)) :
    wordSemIsWordLoc w = true := by
  cases w with
  | word value => rfl
  | loc block offset =>
      simp only [wordGenGcMove] at h
      repeat' (split at h) <;> simp_all [wordSemIsWordLoc]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_IMP_isWord"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_imp_isWord {width : Nat} [NeZero width] (conf : Config) (c i pa old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (gs rs : BitVec width)
    (w : WordLocW width) (i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (h : wordGenGcPartialMove conf (.word c, i, pa, old, m, dm, gs, rs) = (w, i1, pa1, m1, c1)) :
    wordSemIsWordLoc w = true := by
  cases w with
  | word value => rfl
  | loc block offset =>
      simp only [wordGenGcPartialMove] at h
      repeat' (split at h) <;> simp_all [wordSemIsWordLoc]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
