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

end Flapjack.Compiler.Backend.LabToTarget
