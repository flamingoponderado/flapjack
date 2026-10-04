import Flapjack.Pancake.Proofs.WordConvs.GoodHandlersPasses
import Flapjack.Pancake.Proofs.WordConvs.GoodHandlersSSA
import Flapjack.Pancake.Proofs.WordConvs.NotCreatedTail
import Flapjack.Pancake.Proofs.WordConvs.RemoveMustTerminate

/-!
# `wordConvsProof`: `word_good_handlers` through `word_to_word`

`word_good_handlers_three_to_two_reg_prog` (2290-2299), the `remove_unreach` group
(2361-2395) and `word_good_handlers_word_to_word(_incr)` (2992-3034) of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml`. HOL's
`EVERY (λ(n,m,pp). word_good_handlers n pp) l` is `∀ x ∈ l, goodHandlersHOL x.1 x.2.2 = true`.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordUnreach
  Flapjack.Compiler.Encoders.Asm

/-- Boolean form of `word_good_handlers_three_to_two_reg_prog` (Flapjack infrastructure). -/
theorem goodHandlers_threeToTwoRegProg_eq {width : Nat} [NeZero width] (n : Nat) (b : Bool)
    (ps : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (threeToTwoRegProg b ps) = goodHandlersHOL n ps := by
  cases b <;> simp only [threeToTwoRegProg, Bool.false_eq_true, ↓reduceIte]
  induction ps using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h ps ih =>
    fun_cases threeToTwoReg ps <;> simp_all +zetaDelta [goodHandlersHOL]
    all_goals
      repeat' first
        | (rw [ih _ (by change sizeOf _ < sizeOf _; simp <;> omega)])
        | simp_all +zetaDelta [goodHandlersHOL]
        | split

/-- HOL `word_good_handlers_three_to_two_reg_prog` (`wordConvsProofScript.sml:2290-2299`,
    `[local]`); HOL's free `n b` lead. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_three_to_two_reg_prog" (words_as_type_indexed_bitvec)]
theorem goodHandlers_threeToTwoRegProg {width : Nat} [NeZero width] (n : Nat) (b : Bool) :
    ∀ ps : WordLangProgHOL (BitVec width),
      goodHandlersHOL n (threeToTwoRegProg b ps) = true ↔ goodHandlersHOL n ps = true :=
  fun ps => by rw [goodHandlers_threeToTwoRegProg_eq]

/-- HOL `word_good_handlers_SimpSeq` (`wordConvsProofScript.sml:2361-2370`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_SimpSeq"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_simpSeq {width : Nat} [NeZero width] (n : Nat)
    (ps qs : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n ps = true ∧ goodHandlersHOL n qs = true →
      goodHandlersHOL n (simpSeq ps qs) = true := by
  rintro ⟨firstValid, secondValid⟩
  have rest : ∀ (pr : Nat) (moves : List (Nat × Nat)) (r : WordLangProgHOL (BitVec width)),
      destSeqMove qs = some (pr, moves, r) → goodHandlersHOL n r = true := by
    intro pr moves r hd
    cases qs <;> simp_all [destSeqMove, goodHandlersHOL]
    case move =>
      rw [← hd.2.2]
      simp [goodHandlersHOL]
    case seq first second =>
      cases first <;> simp_all [goodHandlersHOL]
  fun_cases simpSeq ps qs <;> simp_all +zetaDelta [goodHandlersHOL]

/-- HOL `word_good_handlers_Seq_assoc_right` (`wordConvsProofScript.sml:2372-2383`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_Seq_assoc_right" (words_as_type_indexed_bitvec)]
theorem goodHandlers_seqAssocRight {width : Nat} [NeZero width] (n : Nat)
    (ps qs : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n ps = true ∧ goodHandlersHOL n qs = true →
      goodHandlersHOL n (seqAssocRight ps qs) = true := by
  rintro ⟨firstValid, secondValid⟩
  induction ps using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing qs with
  | h first ih =>
    fun_cases seqAssocRight first qs <;> try simp_all +zetaDelta only [goodHandlersHOL]
    all_goals
      repeat' first
        | (apply goodHandlers_simpSeq; constructor)
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [goodHandlersHOL, Bool.and_eq_true]
        | split
        | constructor

/-- HOL `word_good_handlers_remove_unreach` (`wordConvsProofScript.sml:2385-2395`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_remove_unreach"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_removeUnreach {width : Nat} [NeZero width] (n : Nat)
    (ps : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n ps = true → goodHandlersHOL n (removeUnreach ps) = true :=
  fun h => goodHandlers_seqAssocRight n ps .skip ⟨h, rfl⟩

/-- `full_compile_single` keeps `word_good_handlers` of a program (Flapjack infrastructure:
    HOL's per-element step of `word_good_handlers_word_to_word_incr_helper`). -/
theorem goodHandlers_fullCompileSingle {width : Nat} [NeZero width] (tra : Bool)
    (regCount1 ralg : Nat) (asmC : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    goodHandlersHOL p.1.1 p.1.2.2 = true →
      goodHandlersHOL (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC p).1
        (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC p).2.2 = true := by
  rcases p with ⟨⟨name, arity, prog⟩, col⟩
  intro h
  simp only [Compiler.Backend.WordToWord.fullCompileSingle, Compiler.Backend.WordToWord.compileSingle]
  rw [goodHandlers_removeMustTerminate, goodHandlers_wordAlloc, goodHandlers_removeDeadProg]
  apply goodHandlers_removeUnreach
  rw [goodHandlers_threeToTwoRegProg, word_good_handlers_copy_prop,
    word_good_handlers_word_common_subexp_elim, goodHandlers_removeDeadProg,
    goodHandlers_fullSsaCcTrans, goodHandlers_instSelect]
  exact goodHandlers_compileExp name prog h

/-- HOL `word_good_handlers_word_to_word_incr_helper` (`wordConvsProofScript.sml:2992-3013`,
    `[local]`); HOL's free `progs tra reg_count1 ralg asm_c` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_word_to_word_incr_helper" (words_as_type_indexed_bitvec)]
theorem goodHandlers_wordToWord_incrHelper {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (tra : Bool) (regCount1 ralg : Nat)
    (asmC : AsmConfigExact width) :
    ∀ oracles : List (Option (Spt Nat)), progs.length = oracles.length →
      (∀ x ∈ progs, goodHandlersHOL x.1 x.2.2 = true) →
      ∀ x ∈ (progs.zip oracles).map
          (Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC),
        goodHandlersHOL x.1 x.2.2 = true := by
  intro oracles _ hp x hx
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
  exact goodHandlers_fullCompileSingle tra regCount1 ralg asmC p (hp _ (List.of_mem_zip hp').1)

/-- HOL `word_good_handlers_word_to_word_incr` (`wordConvsProofScript.sml:3015-3023`); HOL's
    free `progs tra reg_count1 ralg asm_c` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_word_to_word_incr" (words_as_type_indexed_bitvec)]
theorem goodHandlers_wordToWord_incr {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (tra : Bool) (regCount1 ralg : Nat)
    (asmC : AsmConfigExact width) :
    (∀ x ∈ progs, goodHandlersHOL x.1 x.2.2 = true) →
      ∀ x ∈ progs.map (fun p =>
          Compiler.Backend.WordToWord.fullCompileSingle tra regCount1 ralg asmC (p, none)),
        goodHandlersHOL x.1 x.2.2 = true := by
  intro hp x hx
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
  exact goodHandlers_fullCompileSingle tra regCount1 ralg asmC (p, none) (hp p hp')

/-- HOL `word_good_handlers_word_to_word` (`wordConvsProofScript.sml:3025-3034`); HOL's free
    `progs wc ac` are explicit and `compile` is the tagged `word_to_word$compile`. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_word_to_word"
  (words_as_type_indexed_bitvec)]
theorem goodHandlers_wordToWord {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wc : Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact width) :
    (∀ x ∈ progs, goodHandlersHOL x.1 x.2.2 = true) →
      ∀ x ∈ (Compiler.Backend.WordToWord.compile wc ac progs).2,
        goodHandlersHOL x.1 x.2.2 = true := by
  intro hp
  exact goodHandlers_wordToWord_incrHelper progs _ _ _ ac _
    (Compiler.Backend.WordToWord.compile_zip_length wc progs).symm hp

end Flapjack.WordConvs
