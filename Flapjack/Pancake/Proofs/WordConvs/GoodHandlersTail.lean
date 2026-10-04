import Flapjack.Pancake.Proofs.WordConvs.HandlerPasses
import Flapjack.Pancake.Proofs.WordConvs.GoodHandlersPasses
import Flapjack.Pancake.Proofs.WordConvs.GoodHandlersSSA
import Flapjack.Pancake.Proofs.WordConvs.NotCreatedTail
import Flapjack.Pancake.Proofs.WordConvs.RemoveMustTerminate

/-!
# `wordConvsProof`: `word_good_handlers` through `word_to_word`

`word_good_handlers_word_to_word(_incr)` (2992-3034) of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml`, composed from the per-pass laws
(the inst_select/three_to_two/remove_unreach ones are in `HandlerPasses.lean`). HOL's
`EVERY (λ(n,m,pp). word_good_handlers n pp) l` is `∀ x ∈ l, goodHandlersHOL x.1 x.2.2 = true`.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordUnreach
  Flapjack.Compiler.Encoders.Asm

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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
