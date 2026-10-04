import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Output

/-! Original backend compiler-result conventions. -/
namespace Flapjack.Compiler.Backend.BackendProof
open Flapjack Flapjack.WordConvs Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordInst

/-- Full original result equation and whole-input guard; names, labels and all
five output conditions retained. The wildcard oracle result is universally
quantified explicitly. No target evaluation or output property is assumed. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "compile_to_word_conventions2" (words_as_type_indexed_bitvec)]
theorem compileToWordConventions2 {width : Nat} [NeZero width] (wc : Config)
    (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat)))
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (compiled : compile wc ac programs = (col, ps))
    (guard : ∀ p ∈ programs, noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32) :
    ps.map Prod.fst = programs.map Prod.fst ∧
    List.Forall₂ labelsRel (programs.map (fun p => extractLabels p.2.2))
      (ps.map (fun p => extractLabels p.2.2)) ∧
    (∀ p ∈ ps,
      flatExpConventions p.2.2 = true ∧
      postAllocConventionsHOL (ac.regCount - (5 + ac.avoidRegs.length)) p.2.2 = true ∧
      ((∀ q ∈ programs, everyInst (fun i => instOkLessExact ac (HolInst.ofWordLangInst i)) q.2.2 = true) ∧
        addrOffsetOk ac 0 = true ∧ hwOffsetOk ac 0 = true ∧ byteOffsetOk ac 0 = true →
        fullInstOkLessExact ac p.2.2 = true) ∧
      (ac.twoRegArith = true → everyInst twoRegInst p.2.2 = true) ∧
      (noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32)) := by
  have result := CompileConventions.compileToWordConventions wc ac programs guard
  have output : (compile wc ac programs).2 = ps := congrArg Prod.snd compiled
  simpa only [output] using result

end Flapjack.Compiler.Backend.BackendProof
