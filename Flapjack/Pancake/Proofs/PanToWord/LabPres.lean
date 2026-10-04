import Flapjack.Pancake.PanToWord
import Flapjack.Pancake.LoopToWord.Proofs.LabPres
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-!
# `pan_to_wordProof`: good handlers, label preservation and label minimum

`pan_to_word_good_handlers` (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:697-705`),
`pan_to_word_compile_lab_pres` (709-722) and `pan_to_word_compile_prog_lab_min` (726-734):
the last stage of `pan_to_word$compile_prog` is `loop_to_word$compile`, so its handler and label
facts carry over, and every function name is at least `crep_to_loop`'s first name offset 60.
HOL's `EVERY (λ(n,m,p). …) l` is `∀ x ∈ l, …` on the components.
-/

namespace Flapjack.PanToWord
open Flapjack Flapjack.LoopToWord Flapjack.Compiler.Encoders.Asm

/-- HOL `pan_to_word_good_handlers` (`pan_to_wordProofScript.sml:697-705`); HOL's free
    `c prog prog'` are explicit and `good_handlers` is the tagged `goodHandlersHOL`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_good_handlers"
  (words_as_type_indexed_bitvec)]
theorem pan_to_word_good_handlers {width : Nat} [NeZero width] (c : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    panToWordCompileProgHOL c prog = prog' → ∀ x ∈ prog', goodHandlersHOL x.1 x.2.2 = true := by
  intro h x hx
  have := loopToWordGoodHandlers _ prog' h
  rw [List.all_eq_true] at this
  exact this x hx

/-- HOL `pan_to_word_compile_lab_pres` (`pan_to_wordProofScript.sml:709-722`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem pan_to_word_compile_lab_pres {width : Nat} [NeZero width] (c : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    panToWordCompileProgHOL c prog = prog' →
    ∀ x ∈ prog',
      (∀ q ∈ extractLabels x.2.2, q.1 = x.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧ (extractLabels x.2.2).Nodup :=
  fun h => loop_to_word_compile_prog_lab_pres _ prog' h

/-- HOL `pan_to_word_compile_prog_lab_min` (`pan_to_wordProofScript.sml:726-734`); HOL's free
    `c pprog wprog` are explicit. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_lab_min"
  (words_as_type_indexed_bitvec)]
theorem pan_to_word_compile_prog_lab_min {width : Nat} [NeZero width] (c : AsmArchitecture)
    (pprog : List (Pancake.PanLang.DeclHOL width))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    panToWordCompileProgHOL c pprog = wprog → ∀ prog ∈ wprog, 60 ≤ prog.1 := by
  intro h
  exact loop_to_word_compile_lab_min _ wprog 60
    ⟨h, crep_to_loop_compile_prog_lab_min c _ _ rfl⟩

end Flapjack.PanToWord
