import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.LabToTarget.CodeSafety
import Flapjack.Compiler.Backend.LabSem.State

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original shared-memory exclusion transport. Encoding bytes and
lengths may differ, but the complete fetched-line relation retains the actual
instruction constructor and operands. The only premise is the original code
similarity/source-safety conjunction; target safety is proved. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "code_similar_IMP_both_no_share_mem" (words_as_type_indexed_bitvec)]
theorem codeSimilar_noShareMem {width : Nat} [NeZero width]
    (code secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar code secList ∧ noShareMemInst code → noShareMemInst secList := by
  intro ⟨hcode, hsafe⟩ p op re address bytes len hfetch
  have hrel := codeSimilar_asmFetchAux p code secList hcode
  cases hsource : asmFetchAux p code with
  | none => simp [hsource, hfetch] at hrel
  | some line =>
    simp only [hsource, hfetch, Option.rel_some_some] at hrel
    cases line with
    | label sid lid count => simp [lineSimilar] at hrel
    | labAsm inst pos instBytes instLen => simp [lineSimilar] at hrel
    | asm inst sourceBytes sourceLen =>
      change inst = .shareMem op re address at hrel
      subst inst
      exact hsafe p op re address sourceBytes sourceLen hsource

/-- Full original disjunctive safety transport. The shared-memory alternative
retains every external FFI-name witness. The Install alternative retains every
source/target word position, encoding byte list and recorded length, which may
differ under line similarity. No alternative is discarded or strengthened. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "code_similar_IMP_both_no_install_or_no_share_mem" (words_as_type_indexed_bitvec)]
theorem codeSimilar_noInstallOrNoShareMem {width : Nat} [NeZero width]
    (code secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (ffiNames : List HolFfiName) :
    codeSimilar code secList ∧ noInstallOrNoShareMem code ffiNames →
      noInstallOrNoShareMem secList ffiNames := by
  intro ⟨hcode, hsafe⟩
  rcases hsafe with ⟨hshare, hnames⟩ | hinstall
  · exact Or.inl ⟨codeSimilar_noShareMem code secList ⟨hcode, hshare⟩, hnames⟩
  · right
    intro p w bytes len hfetch
    have hrel := codeSimilar_asmFetchAux p code secList hcode
    cases hsource : asmFetchAux p code with
    | none => simp [hsource, hfetch] at hrel
    | some line =>
      simp only [hsource, hfetch, Option.rel_some_some] at hrel
      cases line with
      | label sid lid count => simp [lineSimilar] at hrel
      | asm inst instBytes instLen => simp [lineSimilar] at hrel
      | labAsm inst sourcePos sourceBytes sourceLen =>
        change inst = .install at hrel
        subst inst
        exact hinstall p sourcePos sourceBytes sourceLen hsource

end Flapjack.Compiler.Backend.LabToTarget
