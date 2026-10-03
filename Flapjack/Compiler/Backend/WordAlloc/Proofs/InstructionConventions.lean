import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SelectRegAllocCorrect
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef
import Flapjack.Pancake.WordConvs.FullInstOkLess

/-! Original instruction-convention preservation section of word_allocProof.
All instruction predicates use the reviewed exact assembler configuration.
Executable allocator migration remains separate. -/

namespace Flapjack.WordAlloc
open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-- Original pairwise forced-colour separation implication. All list and Spt
carriers are literal, and no word-valued carrier occurs in this statement. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "forced_distinct_col"]
theorem forcedDistinctCol (spcol : Spt Nat) (ls : List (Nat × Nat)) :
    (∀ m ∈ ls, spDefault spcol m.1 = spDefault spcol m.2 → m.1 = m.2) ∧
      (∀ m ∈ ls, m.1 ≠ m.2) →
    ∀ m ∈ ls, totalColour spcol m.1 ≠ totalColour spcol m.2 := by
  rintro ⟨injective, distinct⟩ m member equal
  rw [totalColourAlt] at equal
  simp only [Function.comp_apply] at equal
  have same : spDefault spcol m.1 = spDefault spcol m.2 := by omega
  exact distinct m member (injective m member same)

/-- Flapjack instruction-case factoring for the original program induction.
This helper retains the exact source validity and forced-edge hypotheses. -/
private theorem instructionColour_preserves {width : Nat} [NeZero width]
    (f : Nat → Nat) (c : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (valid : instOkLessExact c (HolInst.ofWordLangInst i) = true)
    (forced : ∀ m ∈ getForced c (.inst i) [], f m.1 ≠ f m.2) :
    instOkLessExact c (HolInst.ofWordLangInst (applyColourInst f i)) = true := by
  cases i with
  | skip => simp [applyColourInst, applyColourInstCore, HolInst.ofWordLangInst, instOkLessExact]
  | const r w => simp [applyColourInst, applyColourInstCore, HolInst.ofWordLangInst, instOkLessExact]
  | arith a =>
      cases a with
      | binop op r1 r2 ri => cases ri <;> simp_all [applyColourInst, applyColourInstCore, applyColourImmCore, HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, instOkLessExact, getForced]
      | shift op r1 r2 ri => cases ri <;> simp_all [applyColourInst, applyColourInstCore, applyColourImmCore, HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, instOkLessExact, getForced, beq_iff_eq]
      | div r1 r2 r3 | longDiv r1 r2 r3 r4 r5 => simp_all [applyColourInst, applyColourInstCore, HolInst.ofWordLangInst, HolArith.ofWordLangArith, instOkLessExact, getForced, beq_iff_eq]
      | longMul r1 r2 r3 r4 | addCarry r1 r2 r3 r4 | addOverflow r1 r2 r3 r4 | subOverflow r1 r2 r3 r4 =>
          cases hisa : c.isa <;> simp_all [applyColourInst, applyColourInstCore, HolInst.ofWordLangInst, HolArith.ofWordLangArith, instOkLessExact, getForced]
  | mem op r a =>
      cases op <;> cases a <;>
        simp_all [applyColourInst, applyColourInstCore, HolInst.ofWordLangInst,
          HolAddr.ofWordLangAddr, instOkLessExact]
  | fp op =>
      cases op <;>
        simp_all [applyColourInst, applyColourInstCore, HolInst.ofWordLangInst,
          instOkLessExact, getForced, beq_iff_eq]
      all_goals by_cases hw : width = 32 <;> simp_all

/-- Original program-colouring instruction-validity implication, retaining both
source premises: source validity and separation of the source forced pairs. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "word_alloc_full_inst_ok_less_lem" (words_as_type_indexed_bitvec)]
theorem applyColour_fullInstOkLess {width : Nat} [NeZero width] (f : Nat → Nat) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (c : AsmConfigExact width),
      fullInstOkLessExact c prog = true ∧
        (∀ m ∈ getForced c prog [], f m.1 ≠ f m.2) →
      fullInstOkLessExact c (applyColour f prog) = true
  | .seq a b, c => by
      rintro ⟨valid, forced⟩
      simp only [getForced] at forced
      have parts := (everyGetForced (fun m => f m.1 ≠ f m.2) c a (getForced c b [])).mp forced
      simp only [fullInstOkLessExactSeq, Bool.and_eq_true] at valid
      simpa [applyColour, fullInstOkLessExactSeq] using
        And.intro (applyColour_fullInstOkLess f a c ⟨valid.1, parts.1⟩)
          (applyColour_fullInstOkLess f b c ⟨valid.2, parts.2⟩)
  | .ite _ _ _ a b, c => by
      rintro ⟨valid, forced⟩
      simp only [getForced] at forced
      have parts := (everyGetForced (fun m => f m.1 ≠ f m.2) c a (getForced c b [])).mp forced
      simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] at valid ⊢
      simpa [applyColour, fullInstOkLessExact, fullInstOkLessWith] using
        And.intro (applyColour_fullInstOkLess f a c ⟨valid.1, parts.1⟩)
          (applyColour_fullInstOkLess f b c ⟨valid.2, parts.2⟩)
  | .mustTerminate a, c => by
      simpa [applyColour, fullInstOkLessExact, fullInstOkLessWith, getForced] using
        applyColour_fullInstOkLess f a c
  | .loop _ a _, c => by
      simpa [applyColour, fullInstOkLessExact, fullInstOkLessWith, getForced] using
        applyColour_fullInstOkLess f a c
  | .call none _ _ none, _ => by simp [applyColour, fullInstOkLessExact, fullInstOkLessWith]
  | .call none _ _ (some (_, _, _, _)), _ => by
      simp [applyColour, fullInstOkLessExact, fullInstOkLessWith]
  | .call (some (_, _, r, _, _)) _ _ none, c => by
      simpa [applyColour, fullInstOkLessExact, fullInstOkLessWith, getForced] using
        applyColour_fullInstOkLess f r c
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)), c => by
      rintro ⟨valid, forced⟩
      simp only [getForced] at forced
      have parts := (everyGetForced (fun m => f m.1 ≠ f m.2) c p (getForced c r [])).mp forced
      simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] at valid
      simpa [applyColour, fullInstOkLessExact, fullInstOkLessWith] using
        And.intro (applyColour_fullInstOkLess f r c ⟨valid.1, parts.2⟩)
          (applyColour_fullInstOkLess f p c ⟨valid.2, parts.1⟩)
  | .inst i, c => by
      rintro ⟨valid, forced⟩
      exact instructionColour_preserves f c i valid forced
  | .shareInst op n exp, c => by
      rintro ⟨valid, _⟩
      cases exp <;> simp_all [fullInstOkLessExact, fullInstOkLessWith, expToAddrHOL,
        applyColour, applyColourExp, applyColourExpCore]
      split at valid <;> simp_all
      rename_i addr base offset address
      split at address <;> simp_all [applyColourExpCore]
  | .skip, _ | .move _ _, _ | .assign _ _, _ | .get _ _, _ | .store _ _, _ | .set _ _, _
  | .alloc _ _, _ | .storeConsts _ _ _ _ _, _ | .raise _, _ | .return _ _, _ | .break _, _
  | .continue _, _ | .tick, _ | .opCurrHeap _ _ _, _ | .locValue _ _, _ | .install _ _ _ _ _, _
  | .codeBufferWrite _ _, _ | .dataBufferWrite _ _, _ | .ffi _ _ _ _ _ _, _ => by
      simp [applyColour, fullInstOkLessExact, fullInstOkLessWith]

/-- Original full allocator preservation theorem. The source validity is the
only premise; successful selection and forced-colour separation are derived
from the existing original allocator correctness theorem and forced-edge facts. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "word_alloc_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem wordAlloc_fullInstOkLess {width : Nat} [NeZero width]
    (fc alg k : Nat) (prog : WordLangProgHOL (BitVec width))
    (col_opt : Option (Spt Nat)) (c : AsmConfigExact width)
    (valid : fullInstOkLessExact c prog = true) :
    fullInstOkLessExact c (wordAlloc fc c alg k prog col_opt) = true := by
  have oracle : ∀ out, oracleColourOk k col_opt (getClashTree prog []) prog
      (getForced c prog []) = some out → fullInstOkLessExact c out = true := by
    intro out run
    unfold oracleColourOk at run
    split at run <;> try dsimp only at run
    · contradiction
    · split at run <;> try dsimp only at run
      · split at run <;> try dsimp only at run
        · rename_i colour accepted bounded
          cases run
          apply applyColour_fullInstOkLess
          refine ⟨valid, ?_⟩
          intro m member
          simp only [Bool.and_eq_true] at bounded
          have separated := List.all_eq_true.mp bounded.2 m member
          simpa using separated
        · contradiction
      · contradiction
  unfold wordAlloc
  dsimp only
  cases run : oracleColourOk k col_opt (getClashTree prog []) prog (getForced c prog []) with
  | some out => exact oracle out run
  | none =>
      dsimp only
      cases getHeuristics alg fc prog with
      | mk moves costs =>
        dsimp only
        obtain ⟨colour, live, flive, selected, _, _, _, separated⟩ :=
          selectRegAllocCorrect alg costs k moves (getClashTree prog []) (getForced c prog [])
            (getStackOnly prog) (getForcedInGetClashTree prog [] c)
        rw [selected]
        apply applyColour_fullInstOkLess
        exact ⟨valid, forcedDistinctCol colour (getForced c prog [])
          ⟨separated, getForcedPairwiseDistinct c prog [] (by simp)⟩⟩

end Flapjack.WordAlloc
