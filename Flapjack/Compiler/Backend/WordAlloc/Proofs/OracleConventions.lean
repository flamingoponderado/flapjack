import Flapjack.Compiler.Backend.WordAlloc.OracleColour
import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CallArgumentConventions

namespace Flapjack.WordAlloc
open Flapjack

/-- Flapjack extraction of physical fixation from the actual original oracle
entry check. This is infrastructure, not an additional acceptance premise. -/
private theorem evenColour_fixes (colour : Spt Nat)
    (valid : everyEvenColour colour = true) (x : Nat) (physical : isPhyVar x = true) :
    totalColour colour x = x := by
  cases lookup : sptLookup x colour with
  | none => simp [totalColour, lookup, physical]
  | some value =>
      have member := (sptMemToAList colour x value).mpr lookup
      have entry := (List.all_eq_true.mp valid) (x, value) member
      have valueEq : value = x / 2 := by
        simpa [physical] using entry
      simp only [totalColour, lookup, valueEq]
      simp [isPhyVar] at physical
      omega

/-- Original oracle acceptance implication with the complete source
pre-convention and complete target post-convention. Fixation and physical
output are derived from the literal validator, never supplied by the caller. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem oracleColourOk_conventions {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (k : Nat)
    (colOpt : Option (Spt Nat)) (lt : List (Spt Unit × Spt Unit))
    (ls : List (Nat × Nat)) (x : WordLangProgHOL (BitVec width)) :
    preAllocConventionsHOL prog = true ∧
      oracleColourOk k colOpt (getClashTree prog lt) prog ls = some x →
      postAllocConventionsHOL k x = true := by
  rintro ⟨pre, accepted⟩
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at pre
  cases colOpt with
  | none => simp [oracleColourOk] at accepted
  | some colour =>
      simp only [oracleColourOk] at accepted
      split at accepted
      next guard =>
        split at accepted
        next postGuard =>
          cases accepted
          simp only [Bool.and_eq_true] at guard postGuard
          simp only [postAllocConventionsHOL, Bool.and_eq_true]
          refine ⟨everyVar_isPhyVar_totalColour colour prog, postGuard.1, ?_⟩
          apply callArgConvention_preservation
          refine ⟨?_, pre.2⟩
          apply everyVarMono (fun _ => true) prog _
          refine ⟨?_, everyVarTrue prog⟩
          intro name _
          by_cases physical : isPhyVar name = true
          · simp only [physical, Bool.not_true, Bool.false_or, beq_iff_eq]
            exact evenColour_fixes colour guard.1 name physical
          · simp [physical]
        next => simp at accepted
      next => simp at accepted

end Flapjack.WordAlloc
