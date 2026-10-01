import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabSem.Navigation

/-! Navigation preservation uses the executed native navigation definitions.
Encoding bytes, lengths and resolved positions do not affect either search. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "code_similar_IMP_asm_fetch_aux_line_similar" (words_as_type_indexed_bitvec)]
theorem codeSimilar_asmFetchAux {width : Nat} [NeZero width] (pc : Nat)
    (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar c1 c2 → Option.Rel lineSimilar (asmFetchAux pc c1) (asmFetchAux pc c2) := by
  induction c1 generalizing pc c2 with
  | nil =>
    cases c2 <;> simp [codeSimilar, asmFetchAux]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      rcases sec with ⟨sid, lines⟩
      rcases sec' with ⟨sid', lines'⟩
      rcases h with ⟨htail, hlines, hsid⟩
      simp only at hsid hlines
      subst sid'
      induction hlines generalizing pc with
      | nil => simpa only [asmFetchAux] using ih pc rest' htail
      | @cons x y xs ys hxy hrel ihlines =>
        cases x <;> cases y <;> simp only [lineSimilar] at hxy <;> try contradiction
        all_goals simp only [asmFetchAux, isLabelHOL, Bool.false_eq_true, ↓reduceIte]
        all_goals first
          | exact ihlines pc
          | split
            · exact .some hxy
            · exact ihlines (pc - 1)

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "code_similar_loc_to_pc" (words_as_type_indexed_bitvec)]
theorem codeSimilar_locToPc {width : Nat} [NeZero width] (sectionId labelId : Nat)
    (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    codeSimilar c1 c2 → locToPc sectionId labelId c1 = locToPc sectionId labelId c2 := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp [codeSimilar, locToPc]
  | cons sec rest ih =>
    cases c2 with
    | nil => simp [codeSimilar]
    | cons sec' rest' =>
      intro h
      rcases sec with ⟨sid, lines⟩
      rcases sec' with ⟨sid', lines'⟩
      rcases h with ⟨htail, hlines, hsid⟩
      simp only at hsid hlines
      subst sid'
      induction hlines with
      | nil => simp [locToPc, ih rest' htail]
      | @cons x y xs ys hxy hrel ihlines =>
        cases x <;> cases y <;> simp only [lineSimilar] at hxy <;> try contradiction
        all_goals first
          | rcases hxy with ⟨rfl, rfl⟩; simp [locToPc, isLabelHOL, ihlines]
          | simp [locToPc, isLabelHOL, ihlines]

end Flapjack.Compiler.Backend.LabToTarget
