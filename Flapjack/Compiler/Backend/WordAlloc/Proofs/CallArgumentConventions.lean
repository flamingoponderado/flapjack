import Flapjack.Compiler.Backend.WordAlloc.Proofs.ColourOccurrences
import Flapjack.Pancake.WordConvs

/-! Original call argument convention preservation under occurrence-local
fixation of physical registers. -/
namespace Flapjack.WordAlloc
open Flapjack

/-- Flapjack Boolean rendering of the original physical-register implication. -/
private def fixesPhysical (f : Nat → Nat) (x : Nat) : Bool :=
  !isPhyVar x || (f x == x)

/-- Flapjack instruction case infrastructure; fixation is required only at
registers occurring in the instruction, as in the original premise. -/
private theorem instConvention_colour {width : Nat} [NeZero width]
    (f : Nat → Nat) (i : WordLangInst (BitVec width))
    (occurs : everyVarInstHOL (fixesPhysical f) i = true)
    (valid : instArgConvention i = true) :
    instArgConvention (applyColourInst f i) = true := by
  cases i with
  | skip | const _ _ =>
      simp [instArgConvention, applyColourInst, applyColourInstCore]
  | mem op r addr =>
      cases op <;> cases addr <;>
        simp [instArgConvention, applyColourInst, applyColourInstCore]
  | fp op =>
      cases op <;> simp [instArgConvention, applyColourInst, applyColourInstCore]
  | arith a =>
      cases a with
      | binop op r1 r2 ri =>
          cases ri <;> simp [instArgConvention, applyColourInst, applyColourInstCore,
            applyColourImmCore]
      | div _ _ _ =>
          simp [instArgConvention, applyColourInst, applyColourInstCore]
      | shift op r1 r2 ri =>
          cases ri <;> simp_all [everyVarInstHOL, everyVarImmHOL,
            instArgConvention, applyColourInst, applyColourInstCore,
            applyColourImmCore, fixesPhysical, isPhyVar]
      | longMul _ _ _ _ | longDiv _ _ _ _ _ | addCarry _ _ _ _
      | addOverflow _ _ _ _ | subOverflow _ _ _ _ =>
          simp_all [everyVarInstHOL, instArgConvention, applyColourInst,
            applyColourInstCore, fixesPhysical, isPhyVar]

/-- Flapjack canonical argument-list infrastructure. The original occurrence
premise fixes every element of the physical-register sequence. -/
private theorem canonicalList_colour (f : Nat → Nat) (xs : List Nat) (offset : Nat)
    (occurs : xs.all (fixesPhysical f) = true)
    (valid : xs = (List.range xs.length).map (fun x => 2 * (x + offset))) :
    xs.map f = xs := by
  have pointwise : ∀ x ∈ xs, f x = id x := by
    intro x member
    have localFix := (List.all_eq_true.mp occurs) x member
    have physical : isPhyVar x = true := by
      rw [valid] at member
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
      simp [isPhyVar]
    simpa [fixesPhysical, physical] using localFix
  exact (List.map_congr_left pointwise).trans (List.map_id xs)

/-- Original two-premise theorem. Physical-register fixation is required only
at source occurrences; no global fixation or target convention is assumed.
The positive-width native instruction clauses coincide with the HOL clauses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "call_arg_convention_preservation" (words_as_type_indexed_bitvec)]
theorem callArgConvention_preservation {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (f : Nat → Nat) :
    everyVarHOL (fun x => !isPhyVar x || (f x == x)) prog = true ∧
      callArgConventionHOL prog = true →
      callArgConventionHOL (applyColour f prog) = true := by
  change everyVarHOL (fixesPhysical f) prog = true ∧ _ → _
  induction prog using callArgConventionHOL.induct
  case case1 i =>
    simp only [everyVarHOL, callArgConventionHOL, applyColour]
    rintro ⟨occurs, valid⟩
    exact instConvention_colour f i occurs valid
  case case2 label values =>
    simp only [everyVarHOL, callArgConventionHOL, applyColour,
      Bool.and_eq_true, beq_iff_eq, List.length_map]
    rintro ⟨⟨_, occurs⟩, valid⟩
    exact (canonicalList_colour f values 1 occurs valid).trans valid
  case case8 target args handler =>
    cases handler with
    | none =>
      simp only [everyVarHOL, callArgConventionHOL, applyColour,
        Bool.and_eq_true, beq_iff_eq, List.length_map, and_true]
      rintro ⟨occurs, valid⟩
      exact (canonicalList_colour f args 0 occurs (by simpa using valid)).trans valid
    | some h =>
      obtain ⟨v, body, lab, loc⟩ := h
      simp only [everyVarHOL, callArgConventionHOL, applyColour,
        Bool.and_eq_true, beq_iff_eq, List.length_map, and_true]
      rintro ⟨occurs, valid⟩
      exact (canonicalList_colour f args 0 occurs (by simpa using valid)).trans valid
  case case9 target args handler values names retBody lab loc ihRet ihHandler =>
    cases handler with
    | none =>
      simp only [everyVarHOL, callArgConventionHOL, applyColour,
        Bool.and_eq_true, beq_iff_eq, List.length_map, and_true]
      rintro ⟨⟨occArgs, ⟨⟨occVals, _⟩, occBody⟩⟩, ⟨⟨validArgs, validVals⟩, validBody⟩⟩
      exact ⟨⟨(canonicalList_colour f args 1 occArgs validArgs).trans validArgs,
        (canonicalList_colour f values 1 occVals validVals).trans validVals⟩,
        ihRet ⟨occBody, validBody⟩⟩
    | some h =>
      obtain ⟨v, body, handlerLab, handlerLoc⟩ := h
      simp only [everyVarHOL, callArgConventionHOL, applyColour,
        Bool.and_eq_true, beq_iff_eq, List.length_map] at ihHandler ⊢
      rintro ⟨⟨occArgs, ⟨⟨⟨occVals, _⟩, occRet⟩, occV, occBody⟩⟩,
        ⟨⟨⟨validArgs, validVals⟩, validRet⟩, validV, validBody⟩⟩
      have fixedV : f v = 2 := by
        subst v
        simpa [fixesPhysical, isPhyVar] using occV
      exact ⟨⟨⟨(canonicalList_colour f args 1 occArgs validArgs).trans validArgs,
        (canonicalList_colour f values 1 occVals validVals).trans validVals⟩,
        ihRet ⟨occRet, validRet⟩⟩, fixedV, ihHandler ⟨occBody, validBody⟩⟩
  case case14 t _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases t <;> simp_all [everyVarHOL, callArgConventionHOL, applyColour]
    all_goals exfalso
    all_goals rename_i impossible
    all_goals first
      | exact impossible _ _ _ _ rfl rfl rfl rfl
      | exact impossible _ _ _ _ _ rfl rfl rfl rfl rfl
      | exact impossible _ _ _ _ _ _ rfl rfl rfl rfl rfl
      | exact impossible _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  all_goals simp only [callArgConventionHOL, everyVarHOL, applyColour,
    Bool.and_eq_true, beq_iff_eq]
  all_goals intro h
  all_goals simp_all [fixesPhysical, isPhyVar]
  all_goals aesop

end Flapjack.WordAlloc
